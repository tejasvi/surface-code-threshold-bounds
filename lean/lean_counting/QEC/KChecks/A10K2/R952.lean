import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3808 = true := by
  decide +kernel

theorem tot3808 : totK PA10K2 A10K2.t3808 = [0, 0, 0, 516443126182, 1827744042029, 2043246352198, 731023075832, 51277816879, 0, 0] := by
  decide +kernel

theorem rows3809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3809 = true := by
  decide +kernel

theorem tot3809 : totK PA10K2 A10K2.t3809 = [0, 0, 302616931391, 1200396860161, 1785642098100, 1290966632607, 405042638723, 32539518428, 0, 0] := by
  decide +kernel

theorem rows3810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3810 = true := by
  decide +kernel

theorem tot3810 : totK PA10K2 A10K2.t3810 = [0, 0, 458388819914, 1772133008117, 2003683008007, 574939167360, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows3811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3811 = true := by
  decide +kernel

theorem tot3811 : totK PA10K2 A10K2.t3811 = [0, 0, 0, 651443901190, 2052885594883, 1634277548552, 327538943693, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
