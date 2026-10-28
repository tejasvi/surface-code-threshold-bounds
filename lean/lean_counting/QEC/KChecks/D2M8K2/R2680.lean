import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10720 = true := by
  decide +kernel

theorem tot10720 : totK PD2M8K2 D2M8K2.t10720 = [0, 0, 78585949532, 333179653258, 388877151134, 76546348674, 1310517177, 0] := by
  decide +kernel

theorem rows10721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10721 = true := by
  decide +kernel

theorem tot10721 : totK PD2M8K2 D2M8K2.t10721 = [0, 0, 62027068792, 356520630062, 439127596907, 45909914446, 0, 0] := by
  decide +kernel

theorem rows10722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10722 = true := by
  decide +kernel

theorem tot10722 : totK PD2M8K2 D2M8K2.t10722 = [0, 0, 186816353270, 460811227319, 261733518021, 22467740698, 0, 0] := by
  decide +kernel

theorem rows10723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10723 = true := by
  decide +kernel

theorem tot10723 : totK PD2M8K2 D2M8K2.t10723 = [0, 0, 166106579571, 471746389031, 254400208999, 16270752253, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
