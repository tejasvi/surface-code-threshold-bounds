import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6936 = true := by
  decide +kernel

theorem tot6936 : totK PD2M8K2 D2M8K2.t6936 = [0, 181818599164, 468259563524, 256147093209, 23332966453, 0, 0, 0] := by
  decide +kernel

theorem rows6937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6937 = true := by
  decide +kernel

theorem tot6937 : totK PD2M8K2 D2M8K2.t6937 = [0, 167361577328, 469354959941, 249371751604, 15080892866, 0, 0, 0] := by
  decide +kernel

theorem rows6938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6938 = true := by
  decide +kernel

theorem tot6938 : totK PD2M8K2 D2M8K2.t6938 = [0, 0, 278132610408, 508596332325, 116205191274, 1129489618, 0, 0] := by
  decide +kernel

theorem rows6939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6939 = true := by
  decide +kernel

theorem tot6939 : totK PD2M8K2 D2M8K2.t6939 = [0, 52721596474, 245196626535, 415864902936, 161200695898, 7938259948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
