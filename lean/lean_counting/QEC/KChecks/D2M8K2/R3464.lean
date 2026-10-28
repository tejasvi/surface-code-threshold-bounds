import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13856 = true := by
  decide +kernel

theorem tot13856 : totK PD2M8K2 D2M8K2.t13856 = [174538157248, 467567194070, 242224080827, 16058340807, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13857 = true := by
  decide +kernel

theorem tot13857 : totK PD2M8K2 D2M8K2.t13857 = [88193270072, 357410186315, 360036590628, 97983025083, 13132762340, 0, 0, 0] := by
  decide +kernel

theorem rows13858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13858 = true := by
  decide +kernel

theorem tot13858 : totK PD2M8K2 D2M8K2.t13858 = [0, 161735801713, 455396241691, 264741760751, 16253030987, 0, 0, 0] := by
  decide +kernel

theorem rows13859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13859 = true := by
  decide +kernel

theorem tot13859 : totK PD2M8K2 D2M8K2.t13859 = [28108375666, 209054524142, 442858746152, 201531534485, 8209296672, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
