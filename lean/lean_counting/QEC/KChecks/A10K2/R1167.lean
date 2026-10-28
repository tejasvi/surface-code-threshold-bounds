import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4668 = true := by
  decide +kernel

theorem tot4668 : totK PA10K2 A10K2.t4668 = [0, 0, 355606586505, 1314457110077, 1816647265524, 966600297777, 167715549196, 6121173289, 0, 0] := by
  decide +kernel

theorem rows4669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4669 = true := by
  decide +kernel

theorem tot4669 : totK PA10K2 A10K2.t4669 = [0, 0, 385582897690, 1660430286010, 2128109406325, 706769492824, 32712955001, 0, 0, 0] := by
  decide +kernel

theorem rows4670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4670 = true := by
  decide +kernel

theorem tot4670 : totK PA10K2 A10K2.t4670 = [0, 468537272203, 1796269409085, 1808532396828, 490018072697, 184006988889, 34917220296, 0, 0, 0] := by
  decide +kernel

theorem rows4671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4671 = true := by
  decide +kernel

theorem tot4671 : totK PA10K2 A10K2.t4671 = [0, 309417675788, 1234943135280, 1896975901309, 1133400612959, 180741589526, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
