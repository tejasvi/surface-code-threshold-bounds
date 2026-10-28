import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9232 = true := by
  decide +kernel

theorem tot9232 : totK PD2M8K2 D2M8K2.t9232 = [180613305024, 433330009655, 274590460362, 30091733556, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9233 = true := by
  decide +kernel

theorem tot9233 : totK PD2M8K2 D2M8K2.t9233 = [72780203754, 374024231714, 369676894455, 64205173019, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows9234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9234 = true := by
  decide +kernel

theorem tot9234 : totK PD2M8K2 D2M8K2.t9234 = [0, 247012717106, 492332003248, 155975708565, 8423393484, 0, 0, 0] := by
  decide +kernel

theorem rows9235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9235 = true := by
  decide +kernel

theorem tot9235 : totK PD2M8K2 D2M8K2.t9235 = [121752865925, 354059315582, 317982483824, 84916328137, 3462014130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
