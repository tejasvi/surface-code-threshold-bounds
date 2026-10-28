import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5936 = true := by
  decide +kernel

theorem tot5936 : totK PD2M8K2 D2M8K2.t5936 = [0, 178986916693, 465138580442, 220358056002, 12667552787, 0, 0, 0] := by
  decide +kernel

theorem rows5937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5937 = true := by
  decide +kernel

theorem tot5937 : totK PD2M8K2 D2M8K2.t5937 = [0, 193849689959, 479067069298, 214269656075, 12413128817, 0, 0, 0] := by
  decide +kernel

theorem rows5938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5938 = true := by
  decide +kernel

theorem tot5938 : totK PD2M8K2 D2M8K2.t5938 = [0, 131701560160, 433535040344, 310240921529, 24559579412, 0, 0, 0] := by
  decide +kernel

theorem rows5939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5939 = true := by
  decide +kernel

theorem tot5939 : totK PD2M8K2 D2M8K2.t5939 = [0, 19983817196, 287825793277, 490525251755, 95651792104, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
