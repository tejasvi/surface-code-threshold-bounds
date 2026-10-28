import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6352 = true := by
  decide +kernel

theorem tot6352 : totK PA10K2 A10K2.t6352 = [142039744084, 900104990241, 1991338065044, 1421285551310, 248638969737, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6353 = true := by
  decide +kernel

theorem tot6353 : totK PA10K2 A10K2.t6353 = [441166957666, 1838248188659, 2133686293709, 693915637420, 39934856358, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6354 = true := by
  decide +kernel

theorem tot6354 : totK PA10K2 A10K2.t6354 = [0, 625181353410, 2135297235110, 1955736942123, 420936710816, 12833185571, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6355 = true := by
  decide +kernel

theorem tot6355 : totK PA10K2 A10K2.t6355 = [0, 447918905052, 1644792877708, 1931724812477, 754317080447, 69643905659, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
