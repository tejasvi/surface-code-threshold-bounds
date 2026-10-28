import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6840 = true := by
  decide +kernel

theorem tot6840 : totK PD2M8K2 D2M8K2.t6840 = [49818148943, 223017294826, 424750309425, 200098669709, 9353868799, 0, 0, 0] := by
  decide +kernel

theorem rows6841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6841 = true := by
  decide +kernel

theorem tot6841 : totK PD2M8K2 D2M8K2.t6841 = [179107031720, 458722101594, 254413256171, 22948040567, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6842 = true := by
  decide +kernel

theorem tot6842 : totK PD2M8K2 D2M8K2.t6842 = [197475585436, 477442279096, 221764547896, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6843 = true := by
  decide +kernel

theorem tot6843 : totK PD2M8K2 D2M8K2.t6843 = [0, 288761413877, 500261684191, 103471961285, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
