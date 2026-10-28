import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t764 = true := by
  decide +kernel

theorem tot764 : totK PA10K2 A10K2.t764 = [0, 0, 553645941416, 1955574600626, 1963657813166, 421486382246, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t765 = true := by
  decide +kernel

theorem tot765 : totK PA10K2 A10K2.t765 = [0, 319295482399, 1081124596494, 1559261747181, 1398181274622, 522190146641, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t766 = true := by
  decide +kernel

theorem tot766 : totK PA10K2 A10K2.t766 = [0, 448578565548, 1770625282103, 1987331020521, 551390072872, 31923522143, 0, 0, 0, 0] := by
  decide +kernel

theorem rows767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t767 = true := by
  decide +kernel

theorem tot767 : totK PA10K2 A10K2.t767 = [0, 75568977117, 901826824730, 2044383446224, 1493381758638, 335041420816, 20070762815, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
