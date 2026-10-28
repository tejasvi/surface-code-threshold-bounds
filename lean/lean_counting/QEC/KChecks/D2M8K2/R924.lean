import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3696 = true := by
  decide +kernel

theorem tot3696 : totK PD2M8K2 D2M8K2.t3696 = [190993486251, 472520968899, 219686240972, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3697 = true := by
  decide +kernel

theorem tot3697 : totK PD2M8K2 D2M8K2.t3697 = [19356841146, 302863929524, 472915587388, 97889385071, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows3698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3698 = true := by
  decide +kernel

theorem tot3698 : totK PD2M8K2 D2M8K2.t3698 = [0, 200546090303, 470205743282, 192152462472, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows3699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3699 = true := by
  decide +kernel

theorem tot3699 : totK PD2M8K2 D2M8K2.t3699 = [190831994900, 450936305268, 242152109857, 27514656311, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
