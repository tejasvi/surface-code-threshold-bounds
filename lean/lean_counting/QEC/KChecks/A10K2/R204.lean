import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t816 = true := by
  decide +kernel

theorem tot816 : totK PA10K2 A10K2.t816 = [45277493360, 818473867935, 2088760677339, 1591085415589, 377667751403, 25715051306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t817 = true := by
  decide +kernel

theorem tot817 : totK PA10K2 A10K2.t817 = [253046812372, 1215733168565, 2022536881130, 1302433256000, 223976871339, 6032141194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t818 = true := by
  decide +kernel

theorem tot818 : totK PA10K2 A10K2.t818 = [529220833726, 1812407226886, 1952829129367, 598795762546, 43705609746, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t819 = true := by
  decide +kernel

theorem tot819 : totK PA10K2 A10K2.t819 = [84679404475, 949583341790, 2156731771666, 1520148191260, 278898028332, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
