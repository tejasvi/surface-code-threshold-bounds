import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9580 = true := by
  decide +kernel

theorem tot9580 : totK PD2M8K2 D2M8K2.t9580 = [193217774520, 487547417166, 222871965527, 11204801432, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9581 = true := by
  decide +kernel

theorem tot9581 : totK PD2M8K2 D2M8K2.t9581 = [0, 248382521076, 444812883349, 194360224888, 21376388639, 0, 0, 0] := by
  decide +kernel

theorem rows9582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9582 = true := by
  decide +kernel

theorem tot9582 : totK PD2M8K2 D2M8K2.t9582 = [0, 154583783201, 490237610366, 231744348800, 7790548677, 0, 0, 0] := by
  decide +kernel

theorem rows9583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9583 = true := by
  decide +kernel

theorem tot9583 : totK PD2M8K2 D2M8K2.t9583 = [110137281250, 339481986465, 317117888160, 125353983662, 8204069046, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
