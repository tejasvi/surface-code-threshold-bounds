import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1252 = true := by
  decide +kernel

theorem tot1252 : totK PD2M8K2 D2M8K2.t1252 = [173199289669, 460106564524, 254203249379, 22477796781, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1253 = true := by
  decide +kernel

theorem tot1253 : totK PD2M8K2 D2M8K2.t1253 = [193586826366, 475207911460, 220127992710, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1254 = true := by
  decide +kernel

theorem tot1254 : totK PD2M8K2 D2M8K2.t1254 = [30598352162, 313059425229, 462278410768, 93572858103, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows1255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1255 = true := by
  decide +kernel

theorem tot1255 : totK PD2M8K2 D2M8K2.t1255 = [0, 205412289266, 469297470189, 187386908938, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
