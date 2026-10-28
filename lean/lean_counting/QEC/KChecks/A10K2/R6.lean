import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows24 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t24 = true := by
  decide +kernel

theorem tot24 : totK PA10K2 A10K2.t24 = [0, 518309975621, 1915326980922, 1964964563428, 465111111965, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows25 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t25 = true := by
  decide +kernel

theorem tot25 : totK PA10K2 A10K2.t25 = [0, 502587148271, 1809324389745, 1751421703141, 483912761158, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows26 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t26 = true := by
  decide +kernel

theorem tot26 : totK PA10K2 A10K2.t26 = [0, 433234589717, 1602274869878, 1805734288626, 579812259628, 50267370225, 0, 0, 0, 0] := by
  decide +kernel

theorem rows27 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t27 = true := by
  decide +kernel

theorem tot27 : totK PA10K2 A10K2.t27 = [0, 111833022044, 1233869914004, 2226012731231, 906466994989, 77820506896, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
