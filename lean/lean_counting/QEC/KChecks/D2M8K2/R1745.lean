import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6980 = true := by
  decide +kernel

theorem tot6980 : totK PD2M8K2 D2M8K2.t6980 = [0, 0, 232418627803, 478745685863, 151968102408, 4704632337, 0, 0] := by
  decide +kernel

theorem rows6981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6981 = true := by
  decide +kernel

theorem tot6981 : totK PD2M8K2 D2M8K2.t6981 = [0, 0, 207426135474, 488140115019, 172366317077, 5178437131, 0, 0] := by
  decide +kernel

theorem rows6982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6982 = true := by
  decide +kernel

theorem tot6982 : totK PD2M8K2 D2M8K2.t6982 = [0, 0, 199160614721, 466217963463, 220002845043, 15620504087, 0, 0] := by
  decide +kernel

theorem rows6983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6983 = true := by
  decide +kernel

theorem tot6983 : totK PD2M8K2 D2M8K2.t6983 = [0, 89204917003, 234032541318, 345762751752, 210993295539, 17404239282, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
