import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12076 = true := by
  decide +kernel

theorem tot12076 : totK PD2M8K2 D2M8K2.t12076 = [0, 66712467505, 311044721794, 392838692602, 101585611495, 3540641832, 0, 0] := by
  decide +kernel

theorem rows12077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12077 = true := by
  decide +kernel

theorem tot12077 : totK PD2M8K2 D2M8K2.t12077 = [0, 169325983800, 452106394439, 272786455494, 29320126623, 0, 0, 0] := by
  decide +kernel

theorem rows12078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12078 = true := by
  decide +kernel

theorem tot12078 : totK PD2M8K2 D2M8K2.t12078 = [0, 177550997700, 470521604431, 237131240692, 13810080266, 0, 0, 0] := by
  decide +kernel

theorem rows12079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12079 = true := by
  decide +kernel

theorem tot12079 : totK PD2M8K2 D2M8K2.t12079 = [0, 0, 335169225538, 516468527233, 68781611137, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
