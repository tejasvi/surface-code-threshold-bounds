import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1228 = true := by
  decide +kernel

theorem tot1228 : totK PA10K2 A10K2.t1228 = [0, 0, 503174658288, 1807575466353, 1983827816045, 681166521996, 48164548360, 0, 0, 0] := by
  decide +kernel

theorem rows1229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1229 = true := by
  decide +kernel

theorem tot1229 : totK PA10K2 A10K2.t1229 = [0, 0, 478565594986, 1788247066316, 1967534059305, 522157795653, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows1230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1230 = true := by
  decide +kernel

theorem tot1230 : totK PA10K2 A10K2.t1230 = [0, 0, 147954321173, 1017101953692, 1988326629897, 1323345186326, 291885928835, 20060612110, 0, 0] := by
  decide +kernel

theorem rows1231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1231 = true := by
  decide +kernel

theorem tot1231 : totK PA10K2 A10K2.t1231 = [0, 0, 212290920067, 993589161283, 1894998158160, 1310861774821, 248934327804, 10589884120, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
