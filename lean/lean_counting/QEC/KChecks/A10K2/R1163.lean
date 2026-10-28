import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4652 = true := by
  decide +kernel

theorem tot4652 : totK PA10K2 A10K2.t4652 = [0, 0, 185950034399, 1113964436554, 2100854015194, 1285170456505, 200282011859, 6021244195, 0, 0] := by
  decide +kernel

theorem rows4653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4653 = true := by
  decide +kernel

theorem tot4653 : totK PA10K2 A10K2.t4653 = [0, 0, 0, 599326582992, 2020701006315, 1865224885032, 416278383833, 11864432348, 0, 0] := by
  decide +kernel

theorem rows4654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4654 = true := by
  decide +kernel

theorem tot4654 : totK PA10K2 A10K2.t4654 = [0, 481556365868, 1484062668817, 1396331503537, 588003049895, 558665675630, 344628932980, 43132710386, 0, 0] := by
  decide +kernel

theorem rows4655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4655 = true := by
  decide +kernel

theorem tot4655 : totK PA10K2 A10K2.t4655 = [0, 389811071060, 1706589125448, 2076834018092, 676282546504, 25353074737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
