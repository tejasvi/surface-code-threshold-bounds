import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11868 = true := by
  decide +kernel

theorem tot11868 : totK PD2M8K2 D2M8K2.t11868 = [68412647006, 361243007339, 380768616581, 70218376000, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows11869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11869 = true := by
  decide +kernel

theorem tot11869 : totK PD2M8K2 D2M8K2.t11869 = [0, 196052904317, 467866472024, 190495107156, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows11870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11870 = true := by
  decide +kernel

theorem tot11870 : totK PD2M8K2 D2M8K2.t11870 = [160233838038, 450112335861, 276511893470, 29339212061, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11871 = true := by
  decide +kernel

theorem tot11871 : totK PD2M8K2 D2M8K2.t11871 = [189055909089, 457620795841, 235496484274, 16378252205, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
