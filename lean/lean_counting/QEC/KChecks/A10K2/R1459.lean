import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5836 = true := by
  decide +kernel

theorem tot5836 : totK PA10K2 A10K2.t5836 = [0, 0, 490159822480, 1773484322318, 1935625452026, 549520129694, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5837 = true := by
  decide +kernel

theorem tot5837 : totK PA10K2 A10K2.t5837 = [0, 0, 0, 704523624562, 2007139667961, 1588355463769, 347418866850, 25371180993, 0, 0] := by
  decide +kernel

theorem rows5838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5838 = true := by
  decide +kernel

theorem tot5838 : totK PA10K2 A10K2.t5838 = [0, 0, 281829845452, 1213304711701, 1874479388877, 1122428929453, 169285566659, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5839 = true := by
  decide +kernel

theorem tot5839 : totK PA10K2 A10K2.t5839 = [0, 0, 497958302119, 1756179559102, 1853066808401, 612739747058, 52230035883, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
