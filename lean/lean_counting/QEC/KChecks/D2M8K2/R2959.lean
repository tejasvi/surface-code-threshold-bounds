import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11836 = true := by
  decide +kernel

theorem tot11836 : totK PD2M8K2 D2M8K2.t11836 = [0, 0, 64681083429, 359746690182, 347402256351, 54825491094, 1103454931, 0] := by
  decide +kernel

theorem rows11837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11837 = true := by
  decide +kernel

theorem tot11837 : totK PD2M8K2 D2M8K2.t11837 = [0, 0, 91380554513, 416597952796, 326535342768, 26074441745, 0, 0] := by
  decide +kernel

theorem rows11838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11838 = true := by
  decide +kernel

theorem tot11838 : totK PD2M8K2 D2M8K2.t11838 = [0, 0, 252882542699, 471985521266, 174007864372, 6419261094, 0, 0] := by
  decide +kernel

theorem rows11839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11839 = true := by
  decide +kernel

theorem tot11839 : totK PD2M8K2 D2M8K2.t11839 = [0, 0, 220620311828, 495831547511, 167920712244, 2991720150, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
