import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13028 = true := by
  decide +kernel

theorem tot13028 : totK PD2M8K2 D2M8K2.t13028 = [0, 106842647937, 420607118759, 346395097993, 43857359681, 0, 0, 0] := by
  decide +kernel

theorem rows13029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13029 = true := by
  decide +kernel

theorem tot13029 : totK PD2M8K2 D2M8K2.t13029 = [0, 0, 157106558411, 446622013281, 270830373321, 23828799420, 0, 0] := by
  decide +kernel

theorem rows13030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13030 = true := by
  decide +kernel

theorem tot13030 : totK PD2M8K2 D2M8K2.t13030 = [0, 36946381487, 210381224728, 433450048113, 212139951302, 9749326875, 0, 0] := by
  decide +kernel

theorem rows13031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13031 = true := by
  decide +kernel

theorem tot13031 : totK PD2M8K2 D2M8K2.t13031 = [0, 183598937602, 452293497069, 249201249688, 22759740706, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
