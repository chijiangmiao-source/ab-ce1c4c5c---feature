"""强公平请求字段校验：编号形式、义务数量上下限、重复等定位拒绝。"""

import unittest

from app.validation import ValidationError, validate_fairness_payload


def base(**over):
    p = {
        "request_id": "req-001",
        "source_check_id": "CHK-000007",
        "fairness_obligations": ["t1"],
    }
    p.update(over)
    return p


def errors(payload):
    try:
        validate_fairness_payload(payload)
    except ValidationError as e:
        return e.errors
    return []


class TestFairnessPayloadValidation(unittest.TestCase):
    def test_valid(self):
        req = validate_fairness_payload(base())
        self.assertEqual(req["request_id"], "req-001")
        self.assertEqual(req["source_check_id"], "CHK-000007")
        self.assertEqual(req["obligation_ids"], ["t1"])

    def test_missing_request_id(self):
        p = base()
        del p["request_id"]
        self.assertTrue(any("request_id" in e for e in errors(p)))

    def test_bad_request_id_chars(self):
        self.assertTrue(errors(base(request_id="a b")))
        self.assertTrue(errors(base(request_id="../x")))
        self.assertEqual(errors(base(request_id="ok_1-2")), [])

    def test_source_id_form(self):
        for bad in ["FR-000001", "CHK-1", "CHK-abcdef", "chk-000001",
                    "000001", ""]:
            with self.subTest(bad=bad):
                self.assertTrue(
                    any("source_check_id" in e or "编号" in e
                        for e in errors(base(source_check_id=bad))))

    def test_obligation_count_bounds(self):
        self.assertTrue(any("1..4" in e for e in
                            errors(base(fairness_obligations=[]))))
        five = ["t1", "t2", "t3", "t4", "t5"]
        self.assertTrue(any("1..4" in e for e in
                            errors(base(fairness_obligations=five))))
        self.assertEqual(errors(base(fairness_obligations=["a", "b", "c",
                                                           "d"])), [])

    def test_obligation_duplicates(self):
        errs = errors(base(fairness_obligations=["t1", "t1"]))
        self.assertTrue(any("重复" in e for e in errs))

    def test_obligation_must_be_nonempty_string(self):
        errs = errors(base(fairness_obligations=[123]))
        self.assertTrue(errs)
        errs = errors(base(fairness_obligations=[""]))
        self.assertTrue(errs)

    def test_not_object(self):
        self.assertTrue(errors(["nope"]))


if __name__ == "__main__":
    unittest.main()
