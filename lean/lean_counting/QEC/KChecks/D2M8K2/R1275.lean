import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5100 = true := by
  decide +kernel

theorem tot5100 : totK PD2M8K2 D2M8K2.t5100 = [0, 0, 180068682636, 466943228013, 248417007416, 15278595867, 0, 0] := by
  decide +kernel

theorem rows5101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5101 = true := by
  decide +kernel

theorem tot5101 : totK PD2M8K2 D2M8K2.t5101 = [0, 0, 177346668951, 475737093713, 217970586815, 7902352020, 0, 0] := by
  decide +kernel

theorem rows5102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5102 = true := by
  decide +kernel

theorem tot5102 : totK PD2M8K2 D2M8K2.t5102 = [0, 0, 182519928930, 450924866009, 244573979949, 22828318141, 0, 0] := by
  decide +kernel

theorem rows5103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5103 = true := by
  decide +kernel

theorem tot5103 : totK PD2M8K2 D2M8K2.t5103 = [0, 0, 144405161708, 462511936001, 266319431927, 18337374713, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
