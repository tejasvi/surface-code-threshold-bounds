import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4156 = true := by
  decide +kernel

theorem tot4156 : totK PA10K2 A10K2.t4156 = [0, 470800666846, 1812365795120, 2069789419087, 636257933060, 31352465233, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4157 = true := by
  decide +kernel

theorem tot4157 : totK PA10K2 A10K2.t4157 = [0, 0, 582426649356, 2046783540760, 2014809729930, 480014642036, 13231026584, 0, 0, 0] := by
  decide +kernel

theorem rows4158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4158 = true := by
  decide +kernel

theorem tot4158 : totK PA10K2 A10K2.t4158 = [315590801309, 914136781308, 821435138195, 1016788693414, 1259047841830, 515345721022, 49137536365, 0, 0, 0] := by
  decide +kernel

theorem rows4159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4159 = true := by
  decide +kernel

theorem tot4159 : totK PA10K2 A10K2.t4159 = [517845628431, 1812139945628, 1891272905086, 534895952366, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
