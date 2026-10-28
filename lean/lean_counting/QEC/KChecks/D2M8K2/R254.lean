import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1016 = true := by
  decide +kernel

theorem tot1016 : totK PD2M8K2 D2M8K2.t1016 = [0, 208833884616, 474508824986, 210699449656, 12599632882, 0, 0, 0] := by
  decide +kernel

theorem rows1017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1017 = true := by
  decide +kernel

theorem tot1017 : totK PD2M8K2 D2M8K2.t1017 = [0, 156428639911, 479868227221, 243914223560, 14383704323, 0, 0, 0] := by
  decide +kernel

theorem rows1018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1018 = true := by
  decide +kernel

theorem tot1018 : totK PD2M8K2 D2M8K2.t1018 = [0, 171899971786, 440245351011, 269829933698, 27104037771, 0, 0, 0] := by
  decide +kernel

theorem rows1019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1019 = true := by
  decide +kernel

theorem tot1019 : totK PD2M8K2 D2M8K2.t1019 = [0, 170302262395, 467913452177, 242488219803, 14941407165, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
