import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16232 = true := by
  decide +kernel

theorem tot16232 : totK PD2M8K2 D2M8K2.t16232 = [0, 0, 65103140106, 308010557957, 398938182977, 103154398123, 3824247485, 0] := by
  decide +kernel

theorem rows16233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16233 = true := by
  decide +kernel

theorem tot16233 : totK PD2M8K2 D2M8K2.t16233 = [0, 0, 183808494687, 469684856676, 247443969124, 20128547347, 0, 0] := by
  decide +kernel

theorem rows16234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16234 = true := by
  decide +kernel

theorem tot16234 : totK PD2M8K2 D2M8K2.t16234 = [0, 0, 197149340494, 473870612794, 229964042657, 12551143345, 0, 0] := by
  decide +kernel

theorem rows16235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16235 = true := by
  decide +kernel

theorem tot16235 : totK PD2M8K2 D2M8K2.t16235 = [0, 0, 0, 311361106169, 481338954058, 98051269677, 1242138600, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
