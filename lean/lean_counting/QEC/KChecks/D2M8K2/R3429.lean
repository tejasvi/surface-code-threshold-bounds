import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13716 = true := by
  decide +kernel

theorem tot13716 : totK PD2M8K2 D2M8K2.t13716 = [0, 53399450934, 335266602687, 414755262626, 72930082857, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13717 = true := by
  decide +kernel

theorem tot13717 : totK PD2M8K2 D2M8K2.t13717 = [0, 60094570286, 293235786344, 414059805232, 106528379124, 3820764243, 0, 0] := by
  decide +kernel

theorem rows13718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13718 = true := by
  decide +kernel

theorem tot13718 : totK PD2M8K2 D2M8K2.t13718 = [0, 192439777696, 468144160068, 242656172094, 21091113263, 0, 0, 0] := by
  decide +kernel

theorem rows13719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13719 = true := by
  decide +kernel

theorem tot13719 : totK PD2M8K2 D2M8K2.t13719 = [0, 160720040453, 480951877911, 258826024567, 13790854450, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
