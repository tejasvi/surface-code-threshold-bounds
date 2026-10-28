import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7928 = true := by
  decide +kernel

theorem tot7928 : totK PD2M8K2 D2M8K2.t7928 = [0, 0, 334491961684, 521670472160, 75896250866, 0, 0, 0] := by
  decide +kernel

theorem rows7929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7929 = true := by
  decide +kernel

theorem tot7929 : totK PD2M8K2 D2M8K2.t7929 = [0, 0, 194554707243, 501571059753, 184973027670, 5253830308, 0, 0] := by
  decide +kernel

theorem rows7930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7930 = true := by
  decide +kernel

theorem tot7930 : totK PD2M8K2 D2M8K2.t7930 = [0, 0, 170858120645, 440983406943, 229601246585, 17973025655, 0, 0] := by
  decide +kernel

theorem rows7931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7931 = true := by
  decide +kernel

theorem tot7931 : totK PD2M8K2 D2M8K2.t7931 = [0, 0, 64400974753, 349792393387, 358063277635, 63763375733, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
