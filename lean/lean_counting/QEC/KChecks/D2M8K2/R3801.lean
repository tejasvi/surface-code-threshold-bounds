import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15204 = true := by
  decide +kernel

theorem tot15204 : totK PD2M8K2 D2M8K2.t15204 = [0, 155229484744, 450008644929, 278057497650, 21575570854, 0, 0, 0] := by
  decide +kernel

theorem rows15205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15205 = true := by
  decide +kernel

theorem tot15205 : totK PD2M8K2 D2M8K2.t15205 = [0, 0, 224192210997, 496247645888, 165936651138, 6922002537, 0, 0] := by
  decide +kernel

theorem rows15206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15206 = true := by
  decide +kernel

theorem tot15206 : totK PD2M8K2 D2M8K2.t15206 = [0, 87240234242, 318206760499, 380658919913, 102690343956, 1991429766, 0, 0] := by
  decide +kernel

theorem rows15207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15207 = true := by
  decide +kernel

theorem tot15207 : totK PD2M8K2 D2M8K2.t15207 = [0, 173884904024, 474010956047, 260236922724, 21471128534, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
