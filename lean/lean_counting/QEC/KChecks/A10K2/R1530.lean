import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6120 = true := by
  decide +kernel

theorem tot6120 : totK PA10K2 A10K2.t6120 = [0, 0, 409437780291, 1626440080533, 1969747601706, 689806109659, 58003447868, 0, 0, 0] := by
  decide +kernel

theorem rows6121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6121 = true := by
  decide +kernel

theorem tot6121 : totK PA10K2 A10K2.t6121 = [0, 0, 269792744943, 1418467212746, 2040945900927, 695347321945, 45164944030, 0, 0, 0] := by
  decide +kernel

theorem rows6122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6122 = true := by
  decide +kernel

theorem tot6122 : totK PA10K2 A10K2.t6122 = [0, 0, 297273774964, 1207133196850, 1824118629295, 1056416092355, 179533038711, 5546304973, 0, 0] := by
  decide +kernel

theorem rows6123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6123 = true := by
  decide +kernel

theorem tot6123 : totK PA10K2 A10K2.t6123 = [0, 0, 487276792148, 1939053009450, 2132748427976, 530363789450, 6782479114, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
