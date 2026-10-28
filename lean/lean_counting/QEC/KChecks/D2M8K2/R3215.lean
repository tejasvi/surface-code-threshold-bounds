import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12860 = true := by
  decide +kernel

theorem tot12860 : totK PD2M8K2 D2M8K2.t12860 = [0, 67393052748, 268318385355, 382143552640, 172330941688, 8213711289, 0, 0] := by
  decide +kernel

theorem rows12861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12861 = true := by
  decide +kernel

theorem tot12861 : totK PD2M8K2 D2M8K2.t12861 = [0, 179801739092, 444004786528, 265196394581, 28836545722, 0, 0, 0] := by
  decide +kernel

theorem rows12862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12862 = true := by
  decide +kernel

theorem tot12862 : totK PD2M8K2 D2M8K2.t12862 = [0, 156264529942, 454599091202, 273209548807, 22592384582, 0, 0, 0] := by
  decide +kernel

theorem rows12863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12863 = true := by
  decide +kernel

theorem tot12863 : totK PD2M8K2 D2M8K2.t12863 = [0, 0, 213403305630, 482826594416, 181152290427, 8192599454, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
