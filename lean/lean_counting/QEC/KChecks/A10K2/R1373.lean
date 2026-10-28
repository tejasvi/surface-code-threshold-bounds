import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5492 = true := by
  decide +kernel

theorem tot5492 : totK PA10K2 A10K2.t5492 = [0, 0, 299266128110, 1534643707524, 2099240657393, 811489306066, 63281320772, 0, 0, 0] := by
  decide +kernel

theorem rows5493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5493 = true := by
  decide +kernel

theorem tot5493 : totK PA10K2 A10K2.t5493 = [0, 0, 0, 481647119683, 1829039695147, 1864037481690, 485240062535, 31452573850, 0, 0] := by
  decide +kernel

theorem rows5494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5494 = true := by
  decide +kernel

theorem tot5494 : totK PA10K2 A10K2.t5494 = [0, 0, 477162840757, 1699679300220, 1842246942772, 721871832343, 70363809508, 0, 0, 0] := by
  decide +kernel

theorem rows5495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5495 = true := by
  decide +kernel

theorem tot5495 : totK PA10K2 A10K2.t5495 = [0, 0, 293526267267, 1496860618296, 2130864110707, 769986315163, 52620953014, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
