import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7408 = true := by
  decide +kernel

theorem tot7408 : totK PA10K2 A10K2.t7408 = [0, 0, 0, 0, 876265127040, 2288148818605, 1535534787529, 225929271025, 7380853412, 0] := by
  decide +kernel

theorem rows7409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7409 = true := by
  decide +kernel

theorem tot7409 : totK PA10K2 A10K2.t7409 = [0, 0, 0, 597805554384, 2039634038459, 1978675409186, 511659022036, 19579110026, 0, 0] := by
  decide +kernel

theorem rows7410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7410 = true := by
  decide +kernel

theorem tot7410 : totK PA10K2 A10K2.t7410 = [0, 0, 300827602965, 1100491116082, 1599040725022, 1419678158854, 557328071718, 50555834002, 0, 0] := by
  decide +kernel

theorem rows7411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7411 = true := by
  decide +kernel

theorem tot7411 : totK PA10K2 A10K2.t7411 = [0, 0, 476997066642, 1795934693140, 2008934762644, 603432884451, 32318896584, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
