import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9868 = true := by
  decide +kernel

theorem tot9868 : totK PD2M8K2 D2M8K2.t9868 = [0, 191065059825, 462342425950, 240203823584, 20387430297, 0, 0, 0] := by
  decide +kernel

theorem rows9869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9869 = true := by
  decide +kernel

theorem tot9869 : totK PD2M8K2 D2M8K2.t9869 = [0, 189216058583, 477337550509, 226045871883, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows9870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9870 = true := by
  decide +kernel

theorem tot9870 : totK PD2M8K2 D2M8K2.t9870 = [0, 11284885156, 292850594544, 480497434395, 104688271066, 1198073392, 0, 0] := by
  decide +kernel

theorem rows9871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9871 = true := by
  decide +kernel

theorem tot9871 : totK PD2M8K2 D2M8K2.t9871 = [0, 0, 199039240864, 473566120844, 195068868033, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
