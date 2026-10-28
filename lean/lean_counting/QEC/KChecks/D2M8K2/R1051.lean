import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4204 = true := by
  decide +kernel

theorem tot4204 : totK PD2M8K2 D2M8K2.t4204 = [0, 0, 0, 298862846371, 517543060836, 93363434363, 0, 0] := by
  decide +kernel

theorem rows4205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4205 = true := by
  decide +kernel

theorem tot4205 : totK PD2M8K2 D2M8K2.t4205 = [0, 0, 32419875878, 212104005330, 435996058219, 179544765815, 8706415949, 0] := by
  decide +kernel

theorem rows4206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4206 = true := by
  decide +kernel

theorem tot4206 : totK PD2M8K2 D2M8K2.t4206 = [0, 0, 198566501428, 477376423384, 230206739493, 22045224342, 0, 0] := by
  decide +kernel

theorem rows4207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4207 = true := by
  decide +kernel

theorem tot4207 : totK PD2M8K2 D2M8K2.t4207 = [0, 0, 188530027467, 474122309330, 221130784339, 11943121065, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
