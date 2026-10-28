import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5912 = true := by
  decide +kernel

theorem tot5912 : totK PD2M8K2 D2M8K2.t5912 = [0, 166517838695, 476569830347, 239125535713, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows5913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5913 = true := by
  decide +kernel

theorem tot5913 : totK PD2M8K2 D2M8K2.t5913 = [0, 173639433955, 458533407635, 245001142356, 18403075248, 0, 0, 0] := by
  decide +kernel

theorem rows5914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5914 = true := by
  decide +kernel

theorem tot5914 : totK PD2M8K2 D2M8K2.t5914 = [0, 186417734611, 449402970468, 221615808947, 16702988424, 0, 0, 0] := by
  decide +kernel

theorem rows5915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5915 = true := by
  decide +kernel

theorem tot5915 : totK PD2M8K2 D2M8K2.t5915 = [0, 75082883077, 356227981418, 362552101732, 72126821811, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
