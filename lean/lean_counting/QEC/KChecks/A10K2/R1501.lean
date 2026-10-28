import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6004 = true := by
  decide +kernel

theorem tot6004 : totK PA10K2 A10K2.t6004 = [0, 42994989285, 753940131796, 2091626590716, 1426356885132, 259417048368, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6005 = true := by
  decide +kernel

theorem tot6005 : totK PA10K2 A10K2.t6005 = [0, 538828484581, 1919720241497, 1865129398022, 453217786190, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6006 = true := by
  decide +kernel

theorem tot6006 : totK PA10K2 A10K2.t6006 = [0, 257580387599, 1374341112028, 2209098563534, 939906324849, 67068697114, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6007 = true := by
  decide +kernel

theorem tot6007 : totK PA10K2 A10K2.t6007 = [0, 0, 491615798507, 1827272476544, 1831841833248, 483530250616, 30818366867, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
