import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7800 = true := by
  decide +kernel

theorem tot7800 : totK PD2M8K2 D2M8K2.t7800 = [0, 0, 168653805842, 459486058270, 220365472007, 14845936859, 0, 0] := by
  decide +kernel

theorem rows7801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7801 = true := by
  decide +kernel

theorem tot7801 : totK PD2M8K2 D2M8K2.t7801 = [0, 0, 0, 295308678350, 460015398440, 96706610154, 1369150432, 0] := by
  decide +kernel

theorem rows7802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7802 = true := by
  decide +kernel

theorem tot7802 : totK PD2M8K2 D2M8K2.t7802 = [0, 0, 156161144094, 446922532416, 257041171607, 22777510778, 0, 0] := by
  decide +kernel

theorem rows7803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7803 = true := by
  decide +kernel

theorem tot7803 : totK PD2M8K2 D2M8K2.t7803 = [0, 0, 177306955009, 460034294164, 234850886973, 13629821414, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
