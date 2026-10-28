import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11108 = true := by
  decide +kernel

theorem tot11108 : totK PD2M8K2 D2M8K2.t11108 = [0, 44081132587, 203946216068, 405627462414, 206507042741, 16939352947, 0, 0] := by
  decide +kernel

theorem rows11109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11109 = true := by
  decide +kernel

theorem tot11109 : totK PD2M8K2 D2M8K2.t11109 = [0, 204680927276, 485814784516, 208527440920, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows11110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11110 = true := by
  decide +kernel

theorem tot11110 : totK PD2M8K2 D2M8K2.t11110 = [0, 192527614797, 474836765159, 217588155296, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows11111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11111 = true := by
  decide +kernel

theorem tot11111 : totK PD2M8K2 D2M8K2.t11111 = [0, 0, 296342113101, 488954509433, 106806023179, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
