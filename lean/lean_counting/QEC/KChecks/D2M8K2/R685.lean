import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2740 = true := by
  decide +kernel

theorem tot2740 : totK PD2M8K2 D2M8K2.t2740 = [0, 165930123960, 438394315373, 280966507009, 30490141435, 0, 0, 0] := by
  decide +kernel

theorem rows2741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2741 = true := by
  decide +kernel

theorem tot2741 : totK PD2M8K2 D2M8K2.t2741 = [0, 117921825230, 418562383292, 319792808999, 31600709181, 0, 0, 0] := by
  decide +kernel

theorem rows2742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2742 = true := by
  decide +kernel

theorem tot2742 : totK PD2M8K2 D2M8K2.t2742 = [0, 0, 213965231240, 477291465299, 182529804285, 9668735432, 0, 0] := by
  decide +kernel

theorem rows2743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2743 = true := by
  decide +kernel

theorem tot2743 : totK PD2M8K2 D2M8K2.t2743 = [0, 100625761363, 336839361987, 340675056830, 94529425809, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
