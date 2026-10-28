import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7608 = true := by
  decide +kernel

theorem tot7608 : totK PA10K2 A10K2.t7608 = [0, 0, 99047224469, 1111447781108, 2233777106165, 1071596833461, 99566269114, 0, 0, 0] := by
  decide +kernel

theorem rows7609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7609 = true := by
  decide +kernel

theorem tot7609 : totK PA10K2 A10K2.t7609 = [0, 0, 501990865574, 1735467084613, 1883653639311, 751293139345, 128966711574, 6239673734, 0, 0] := by
  decide +kernel

theorem rows7610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7610 = true := by
  decide +kernel

theorem tot7610 : totK PA10K2 A10K2.t7610 = [0, 0, 319364795913, 1492713539988, 2204542152931, 1059329801318, 107546879043, 0, 0, 0] := by
  decide +kernel

theorem rows7611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7611 = true := by
  decide +kernel

theorem tot7611 : totK PA10K2 A10K2.t7611 = [0, 0, 0, 613592017148, 2061909287375, 1955609209512, 426665979889, 13242594235, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
