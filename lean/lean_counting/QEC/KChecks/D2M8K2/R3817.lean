import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15268 = true := by
  decide +kernel

theorem tot15268 : totK PD2M8K2 D2M8K2.t15268 = [0, 0, 19433589518, 314804491483, 478185037675, 88867279087, 1164319620, 0] := by
  decide +kernel

theorem rows15269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15269 = true := by
  decide +kernel

theorem tot15269 : totK PD2M8K2 D2M8K2.t15269 = [0, 0, 32933835765, 281366890938, 469344642779, 118734349158, 4234510686, 0] := by
  decide +kernel

theorem rows15270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15270 = true := by
  decide +kernel

theorem tot15270 : totK PD2M8K2 D2M8K2.t15270 = [0, 0, 201770689340, 483600319409, 216260026668, 9931699895, 0, 0] := by
  decide +kernel

theorem rows15271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15271 = true := by
  decide +kernel

theorem tot15271 : totK PD2M8K2 D2M8K2.t15271 = [0, 0, 140124418844, 442724880285, 266444315942, 15773660181, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
