import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6756 = true := by
  decide +kernel

theorem tot6756 : totK PD2M8K2 D2M8K2.t6756 = [0, 201004546692, 465073956707, 217033723792, 10929898537, 0, 0, 0] := by
  decide +kernel

theorem rows6757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6757 = true := by
  decide +kernel

theorem tot6757 : totK PD2M8K2 D2M8K2.t6757 = [67645289364, 213164463086, 384990792394, 225456435227, 17433533548, 0, 0, 0] := by
  decide +kernel

theorem rows6758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6758 = true := by
  decide +kernel

theorem tot6758 : totK PD2M8K2 D2M8K2.t6758 = [162383527234, 444951010150, 283845295174, 30268796398, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6759 = true := by
  decide +kernel

theorem tot6759 : totK PD2M8K2 D2M8K2.t6759 = [204861684518, 478146031793, 213184788852, 10484158211, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
