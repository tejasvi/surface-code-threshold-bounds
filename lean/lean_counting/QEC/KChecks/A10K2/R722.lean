import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2888 = true := by
  decide +kernel

theorem tot2888 : totK PA10K2 A10K2.t2888 = [297251734964, 1480271605234, 2182049567580, 954627244029, 83396504472, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2889 = true := by
  decide +kernel

theorem tot2889 : totK PA10K2 A10K2.t2889 = [0, 563753865573, 1957018574080, 1834795564725, 474829379864, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2890 = true := by
  decide +kernel

theorem tot2890 : totK PA10K2 A10K2.t2890 = [416446714324, 1557921286055, 1992926073292, 843138865377, 85679764567, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2891 = true := by
  decide +kernel

theorem tot2891 : totK PA10K2 A10K2.t2891 = [498927612862, 1852735667758, 2019875204798, 603666022501, 43664707169, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
