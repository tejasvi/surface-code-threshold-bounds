import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8968 = true := by
  decide +kernel

theorem tot8968 : totK PD2M8K2 D2M8K2.t8968 = [0, 194807754990, 481602182808, 221881967592, 12592010156, 0, 0, 0] := by
  decide +kernel

theorem rows8969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8969 = true := by
  decide +kernel

theorem tot8969 : totK PD2M8K2 D2M8K2.t8969 = [0, 209582218194, 471614096233, 195803300544, 8074108864, 0, 0, 0] := by
  decide +kernel

theorem rows8970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8970 = true := by
  decide +kernel

theorem tot8970 : totK PD2M8K2 D2M8K2.t8970 = [0, 163205205145, 453311750029, 261633217042, 19325516616, 0, 0, 0] := by
  decide +kernel

theorem rows8971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8971 = true := by
  decide +kernel

theorem tot8971 : totK PD2M8K2 D2M8K2.t8971 = [0, 172314681018, 472521243394, 239000388125, 13882341960, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
