import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11736 = true := by
  decide +kernel

theorem tot11736 : totK PD2M8K2 D2M8K2.t11736 = [0, 96336557448, 412689044202, 346551901705, 32366027297, 0, 0, 0] := by
  decide +kernel

theorem rows11737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11737 = true := by
  decide +kernel

theorem tot11737 : totK PD2M8K2 D2M8K2.t11737 = [0, 0, 214491048004, 484567501297, 175905070355, 9587713104, 0, 0] := by
  decide +kernel

theorem rows11738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11738 = true := by
  decide +kernel

theorem tot11738 : totK PD2M8K2 D2M8K2.t11738 = [0, 97024634520, 338507091863, 345588679622, 87592844674, 3462014130, 0, 0] := by
  decide +kernel

theorem rows11739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11739 = true := by
  decide +kernel

theorem tot11739 : totK PD2M8K2 D2M8K2.t11739 = [0, 190294419213, 472513771204, 212426826008, 12420044233, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
