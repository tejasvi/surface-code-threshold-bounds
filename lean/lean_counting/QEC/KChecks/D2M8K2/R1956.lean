import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7824 = true := by
  decide +kernel

theorem tot7824 : totK PD2M8K2 D2M8K2.t7824 = [0, 181698402592, 444515054242, 240455452666, 21467888622, 0, 0, 0] := by
  decide +kernel

theorem rows7825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7825 = true := by
  decide +kernel

theorem tot7825 : totK PD2M8K2 D2M8K2.t7825 = [0, 76992524251, 369732061662, 372708276195, 74891497675, 1096156699, 0, 0] := by
  decide +kernel

theorem rows7826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7826 = true := by
  decide +kernel

theorem tot7826 : totK PD2M8K2 D2M8K2.t7826 = [0, 0, 275901150052, 519672461589, 108065049616, 1067382613, 0, 0] := by
  decide +kernel

theorem rows7827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7827 = true := by
  decide +kernel

theorem tot7827 : totK PD2M8K2 D2M8K2.t7827 = [0, 174823675156, 436022226324, 264061399017, 50566677914, 2813333534, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
