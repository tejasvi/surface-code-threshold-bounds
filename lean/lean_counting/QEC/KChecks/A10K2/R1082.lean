import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4328 = true := by
  decide +kernel

theorem tot4328 : totK PA10K2 A10K2.t4328 = [0, 0, 0, 574555914992, 1963628603182, 1724553008755, 417774392235, 25371180993, 0, 0] := by
  decide +kernel

theorem rows4329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4329 = true := by
  decide +kernel

theorem tot4329 : totK PA10K2 A10K2.t4329 = [0, 0, 292562553233, 1330501880167, 1965589220902, 1039482987562, 170750915046, 5460492893, 0, 0] := by
  decide +kernel

theorem rows4330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4330 = true := by
  decide +kernel

theorem tot4330 : totK PA10K2 A10K2.t4330 = [0, 0, 430118206332, 1720130220723, 1836960892235, 502803511547, 32389629884, 0, 0, 0] := by
  decide +kernel

theorem rows4331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4331 = true := by
  decide +kernel

theorem tot4331 : totK PA10K2 A10K2.t4331 = [0, 0, 153221607906, 910993829343, 2008576124718, 1226931898446, 178895245903, 5705019915, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
