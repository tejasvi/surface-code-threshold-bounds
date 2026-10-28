import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t768 = true := by
  decide +kernel

theorem tot768 : totK PD2M8K2 D2M8K2.t768 = [0, 8125304319, 306383534636, 480849790140, 98198924857, 1198073392, 0, 0] := by
  decide +kernel

theorem rows769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t769 = true := by
  decide +kernel

theorem tot769 : totK PD2M8K2 D2M8K2.t769 = [0, 0, 188835523542, 465454353611, 195490059275, 11991925116, 0, 0] := by
  decide +kernel

theorem rows770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t770 = true := by
  decide +kernel

theorem tot770 : totK PD2M8K2 D2M8K2.t770 = [0, 171103826720, 446461140260, 261111112721, 24078426289, 0, 0, 0] := by
  decide +kernel

theorem rows771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t771 = true := by
  decide +kernel

theorem tot771 : totK PD2M8K2 D2M8K2.t771 = [0, 182537837406, 453115254762, 230304861470, 17038536804, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
