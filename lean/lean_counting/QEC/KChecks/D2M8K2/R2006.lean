import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8024 = true := by
  decide +kernel

theorem tot8024 : totK PD2M8K2 D2M8K2.t8024 = [0, 0, 155674322438, 467564624373, 259640739013, 15054008244, 0, 0] := by
  decide +kernel

theorem rows8025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8025 = true := by
  decide +kernel

theorem tot8025 : totK PD2M8K2 D2M8K2.t8025 = [0, 0, 0, 257999849326, 499054547367, 112854214461, 2240648673, 0] := by
  decide +kernel

theorem rows8026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8026 = true := by
  decide +kernel

theorem tot8026 : totK PD2M8K2 D2M8K2.t8026 = [0, 0, 68122631418, 249833974424, 395254109961, 146707133235, 10668617419, 0] := by
  decide +kernel

theorem rows8027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8027 = true := by
  decide +kernel

theorem tot8027 : totK PD2M8K2 D2M8K2.t8027 = [0, 0, 187831986554, 470797309631, 224236332208, 12733523168, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
