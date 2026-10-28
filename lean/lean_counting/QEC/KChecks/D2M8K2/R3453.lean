import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13812 = true := by
  decide +kernel

theorem tot13812 : totK PD2M8K2 D2M8K2.t13812 = [0, 0, 335359941008, 508185156186, 59267275276, 0, 0, 0] := by
  decide +kernel

theorem rows13813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13813 = true := by
  decide +kernel

theorem tot13813 : totK PD2M8K2 D2M8K2.t13813 = [0, 158316649854, 392891823897, 284122286940, 76463698428, 1415142070, 0, 0] := by
  decide +kernel

theorem rows13814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13814 = true := by
  decide +kernel

theorem tot13814 : totK PD2M8K2 D2M8K2.t13814 = [0, 173130873977, 440954343185, 265349193733, 28459543310, 0, 0, 0] := by
  decide +kernel

theorem rows13815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13815 = true := by
  decide +kernel

theorem tot13815 : totK PD2M8K2 D2M8K2.t13815 = [0, 92515481918, 431698313099, 349803111530, 36822593388, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
