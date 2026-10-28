import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5036 = true := by
  decide +kernel

theorem tot5036 : totK PD2M8K2 D2M8K2.t5036 = [0, 189051660023, 473119294932, 213085527025, 11034354488, 0, 0, 0] := by
  decide +kernel

theorem rows5037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5037 = true := by
  decide +kernel

theorem tot5037 : totK PD2M8K2 D2M8K2.t5037 = [0, 150267198679, 453987724540, 271150008232, 21929265216, 0, 0, 0] := by
  decide +kernel

theorem rows5038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5038 = true := by
  decide +kernel

theorem tot5038 : totK PD2M8K2 D2M8K2.t5038 = [0, 0, 270964542476, 501709216331, 103455136407, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5039 = true := by
  decide +kernel

theorem tot5039 : totK PD2M8K2 D2M8K2.t5039 = [0, 158839781470, 417443117094, 323185051039, 37263182974, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
