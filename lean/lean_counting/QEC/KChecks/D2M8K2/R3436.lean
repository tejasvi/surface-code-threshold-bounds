import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13744 = true := by
  decide +kernel

theorem tot13744 : totK PD2M8K2 D2M8K2.t13744 = [0, 100153354801, 397472713252, 359284076731, 37320424042, 0, 0, 0] := by
  decide +kernel

theorem rows13745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13745 = true := by
  decide +kernel

theorem tot13745 : totK PD2M8K2 D2M8K2.t13745 = [0, 175334545812, 449068702995, 255394065598, 25547917268, 0, 0, 0] := by
  decide +kernel

theorem rows13746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13746 = true := by
  decide +kernel

theorem tot13746 : totK PD2M8K2 D2M8K2.t13746 = [0, 119900797135, 429400433480, 312915116326, 26017578311, 0, 0, 0] := by
  decide +kernel

theorem rows13747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13747 = true := by
  decide +kernel

theorem tot13747 : totK PD2M8K2 D2M8K2.t13747 = [0, 0, 209945947924, 484706938194, 169762370342, 9521435666, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
