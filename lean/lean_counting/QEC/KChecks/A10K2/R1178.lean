import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4712 = true := by
  decide +kernel

theorem tot4712 : totK PA10K2 A10K2.t4712 = [0, 0, 307530512419, 1282623326262, 1938689465282, 1017628600970, 135697006624, 5460492893, 0, 0] := by
  decide +kernel

theorem rows4713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4713 = true := by
  decide +kernel

theorem tot4713 : totK PA10K2 A10K2.t4713 = [0, 0, 488300766439, 1859381773073, 1992872855869, 499820149144, 17643329925, 0, 0, 0] := by
  decide +kernel

theorem rows4714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4714 = true := by
  decide +kernel

theorem tot4714 : totK PA10K2 A10K2.t4714 = [0, 0, 0, 680398177950, 2035538891343, 1676262662688, 400865714212, 25734533292, 0, 0] := by
  decide +kernel

theorem rows4715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4715 = true := by
  decide +kernel

theorem tot4715 : totK PA10K2 A10K2.t4715 = [0, 0, 321041346309, 1127515255416, 1792844287984, 1176866903719, 204435148553, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
