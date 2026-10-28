import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10796 = true := by
  decide +kernel

theorem tot10796 : totK PD2M8K2 D2M8K2.t10796 = [0, 0, 217605053401, 468590033258, 183766955355, 9655709451, 0, 0] := by
  decide +kernel

theorem rows10797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10797 = true := by
  decide +kernel

theorem tot10797 : totK PD2M8K2 D2M8K2.t10797 = [0, 0, 179542968435, 497652838308, 214916958758, 5265834820, 0, 0] := by
  decide +kernel

theorem rows10798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10798 = true := by
  decide +kernel

theorem tot10798 : totK PD2M8K2 D2M8K2.t10798 = [0, 0, 171494738875, 453598285652, 240171422738, 13577881100, 0, 0] := by
  decide +kernel

theorem rows10799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10799 = true := by
  decide +kernel

theorem tot10799 : totK PD2M8K2 D2M8K2.t10799 = [0, 94311201580, 299943940041, 358822508638, 164914515872, 13468148062, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
