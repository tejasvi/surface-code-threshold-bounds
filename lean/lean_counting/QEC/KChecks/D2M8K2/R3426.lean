import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13704 = true := by
  decide +kernel

theorem tot13704 : totK PD2M8K2 D2M8K2.t13704 = [0, 196039264590, 451366014511, 210442108732, 12409643806, 0, 0, 0] := by
  decide +kernel

theorem rows13705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13705 = true := by
  decide +kernel

theorem tot13705 : totK PD2M8K2 D2M8K2.t13705 = [0, 42475731751, 316584477036, 434815929198, 97598239404, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13706 = true := by
  decide +kernel

theorem tot13706 : totK PD2M8K2 D2M8K2.t13706 = [0, 63380760922, 351659848984, 431337104962, 53986544122, 0, 0, 0] := by
  decide +kernel

theorem rows13707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13707 = true := by
  decide +kernel

theorem tot13707 : totK PD2M8K2 D2M8K2.t13707 = [0, 160997896898, 441829732857, 280901946083, 30306979718, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
