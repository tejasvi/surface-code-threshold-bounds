import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2936 = true := by
  decide +kernel

theorem tot2936 : totK PD2M8K2 D2M8K2.t2936 = [0, 261942948702, 443630968409, 193330113948, 21380039407, 0, 0, 0] := by
  decide +kernel

theorem rows2937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2937 = true := by
  decide +kernel

theorem tot2937 : totK PD2M8K2 D2M8K2.t2937 = [0, 172474632662, 500283201959, 224056206601, 7960973547, 0, 0, 0] := by
  decide +kernel

theorem rows2938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2938 = true := by
  decide +kernel

theorem tot2938 : totK PD2M8K2 D2M8K2.t2938 = [102762702211, 321318209338, 324871761203, 140024246679, 8213711289, 0, 0, 0] := by
  decide +kernel

theorem rows2939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2939 = true := by
  decide +kernel

theorem tot2939 : totK PD2M8K2 D2M8K2.t2939 = [164594364570, 440181073516, 280219777892, 30183638042, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
