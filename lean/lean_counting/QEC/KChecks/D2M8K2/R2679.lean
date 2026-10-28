import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10716 = true := by
  decide +kernel

theorem tot10716 : totK PD2M8K2 D2M8K2.t10716 = [0, 0, 128154751257, 442613551233, 297611536899, 18762294916, 0, 0] := by
  decide +kernel

theorem rows10717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10717 = true := by
  decide +kernel

theorem tot10717 : totK PD2M8K2 D2M8K2.t10717 = [0, 0, 0, 313628109636, 485969361212, 84112117115, 1096505104, 0] := by
  decide +kernel

theorem rows10718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10718 = true := by
  decide +kernel

theorem tot10718 : totK PD2M8K2 D2M8K2.t10718 = [0, 0, 153562545122, 381161312392, 251742194850, 69557746423, 3884009855, 0] := by
  decide +kernel

theorem rows10719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10719 = true := by
  decide +kernel

theorem tot10719 : totK PD2M8K2 D2M8K2.t10719 = [0, 0, 173369650633, 467891440918, 232439443827, 13270271918, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
