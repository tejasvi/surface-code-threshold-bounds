import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5996 = true := by
  decide +kernel

theorem tot5996 : totK PA10K2 A10K2.t5996 = [107511406453, 605723204676, 1693883720104, 1822055670934, 501340600670, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5997 = true := by
  decide +kernel

theorem tot5997 : totK PA10K2 A10K2.t5997 = [445387929426, 1643166767798, 1928514985941, 657375787937, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5998 = true := by
  decide +kernel

theorem tot5998 : totK PA10K2 A10K2.t5998 = [267608287982, 1470331197030, 2100141412561, 825946364223, 60970094597, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5999 = true := by
  decide +kernel

theorem tot5999 : totK PA10K2 A10K2.t5999 = [0, 699272228009, 2167315433498, 1572036945675, 255183158916, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
