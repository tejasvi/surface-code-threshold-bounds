import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6120 = true := by
  decide +kernel

theorem tot6120 : totK PD2M8K2 D2M8K2.t6120 = [0, 0, 190380556460, 462467302462, 224105525758, 9930239593, 0, 0] := by
  decide +kernel

theorem rows6121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6121 = true := by
  decide +kernel

theorem tot6121 : totK PD2M8K2 D2M8K2.t6121 = [0, 0, 38228932023, 380013926238, 436523756552, 46103686494, 0, 0] := by
  decide +kernel

theorem rows6122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6122 = true := by
  decide +kernel

theorem tot6122 : totK PD2M8K2 D2M8K2.t6122 = [0, 0, 0, 190757626623, 496194525235, 170074778341, 3647390732, 0] := by
  decide +kernel

theorem rows6123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6123 = true := by
  decide +kernel

theorem tot6123 : totK PD2M8K2 D2M8K2.t6123 = [179984371288, 439406052484, 187861159738, 8381228393, 32599397293, 49492087454, 5886361114, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
